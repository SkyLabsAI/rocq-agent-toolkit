"""
S3 upload utilities.
"""

import io
import logging

import boto3  # type: ignore[import-untyped]
from botocore.exceptions import (  # type: ignore[import-untyped]
    ClientError,
    NoCredentialsError,
)

from backend.config import settings

logger = logging.getLogger(__name__)


def upload_bytes_to_s3(
    file_content: bytes,
    object_key: str,
) -> str | None:
    """
    Upload bytes content to S3 bucket configured in settings.

    Returns the S3 URL if successful, or None if skipped/failed.
    """
    # Prepend folder to object_key
    folder = "rat-jsonls"
    object_key = f"{folder}/{object_key}"

    if not (
        settings.AWS_ACCESS_KEY_ID
        and settings.AWS_SECRET_ACCESS_KEY
        and settings.S3_BUCKET_NAME
    ):
        logger.info("AWS credentials or bucket not configured. Skipping S3 upload.")
        return None

    try:
        s3_client = boto3.client(
            "s3",
            aws_access_key_id=settings.AWS_ACCESS_KEY_ID,
            aws_secret_access_key=settings.AWS_SECRET_ACCESS_KEY,
            region_name=settings.AWS_REGION,
        )

        file_obj = io.BytesIO(file_content)
        s3_client.upload_fileobj(file_obj, settings.S3_BUCKET_NAME, object_key)

        region = settings.AWS_REGION or s3_client.meta.region_name

        if region == "us-east-1":
            url = f"https://{settings.S3_BUCKET_NAME}.s3.amazonaws.com/{object_key}"
        else:
            url = f"https://{settings.S3_BUCKET_NAME}.s3.{region}.amazonaws.com/{object_key}"

        logger.info(
            "Successfully uploaded %s to S3 bucket %s",
            object_key,
            settings.S3_BUCKET_NAME,
        )
        return url

    except NoCredentialsError:
        logger.warning("AWS credentials not available.")
        return None
    except ClientError as e:
        logger.error("AWS ClientError during S3 upload: %s", e)
        return None
    except Exception as e:  # pylint: disable=broad-exception-caught
        logger.error("Unexpected error during S3 upload: %s", e)
        return None


def download_bytes_from_s3(object_key: str) -> bytes | None:
    """
    Download bytes content from the S3 bucket configured in settings.

    The `object_key` should be the logical filename used at ingestion time
    (e.g. the `source_file_name`). This function applies the same folder
    prefixing as `upload_bytes_to_s3`.

    Returns the object bytes if successful, or None if skipped/not found/failed.
    """
    # Prepend folder to object_key (must match upload_bytes_to_s3)
    folder = "rat-jsonls"
    object_key = f"{folder}/{object_key}"
    print(f"Downloading object from S3 bucket {settings.S3_BUCKET_NAME} with key {object_key}")
    if not (
        settings.AWS_ACCESS_KEY_ID
        and settings.AWS_SECRET_ACCESS_KEY
        and settings.S3_BUCKET_NAME
    ):
        logger.info("AWS credentials or bucket not configured. Skipping S3 download.")
        return None

    try:
        s3_client = boto3.client(
            "s3",
            aws_access_key_id=settings.AWS_ACCESS_KEY_ID,
            aws_secret_access_key=settings.AWS_SECRET_ACCESS_KEY,
            region_name=settings.AWS_REGION,
        )

        resp = s3_client.get_object(Bucket=settings.S3_BUCKET_NAME, Key=object_key)
        body = resp.get("Body")
        if body is None:
            logger.warning("S3 get_object response had no Body for key=%s", object_key)
            return None

        data: bytes = body.read()
        logger.info(
            "Successfully downloaded %s from S3 bucket %s",
            object_key,
            settings.S3_BUCKET_NAME,
        )
        return data

    except NoCredentialsError:
        logger.warning("AWS credentials not available.")
        return None
    except ClientError as e:
        # Common cases: NoSuchKey, AccessDenied, NoSuchBucket
        code = (
            (e.response or {}).get("Error", {}).get("Code")  # type: ignore[union-attr]
            if hasattr(e, "response")
            else None
        )
        if code in {"NoSuchKey", "404", "NotFound"}:
            logger.warning("S3 object not found: %s", object_key)
            return None
        logger.error("AWS ClientError during S3 download (key=%s): %s", object_key, e)
        return None
    except Exception as e:  # pylint: disable=broad-exception-caught
        logger.error("Unexpected error during S3 download (key=%s): %s", object_key, e)
        return None
