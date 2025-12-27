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
    except Exception as e:
        logger.error("Unexpected error during S3 upload: %s", e)
        return None
