import '@testing-library/jest-dom';

// Polyfill TextEncoder/TextDecoder if missing (jsdom environment)
if (typeof global.TextEncoder === 'undefined') {
	const { TextEncoder } = require('util');
	global.TextEncoder = TextEncoder;
}
if (typeof global.TextDecoder === 'undefined') {
	const { TextDecoder } = require('util');
	global.TextDecoder = TextDecoder;
}

// Mock react-syntax-highlighter ESM to avoid Jest parsing error
jest.mock('react-syntax-highlighter', () => {
	const React = require('react');
	const MockHighlighter = ({ children }) => React.createElement('pre', { 'data-testid': 'syntax-highlighter' }, children);
	return {
		__esModule: true,
		Light: MockHighlighter,
		Prism: MockHighlighter,
		default: MockHighlighter,
	};
});

// Also mock the ESM styles import path used by code viewer
jest.mock('react-syntax-highlighter/dist/esm/styles/prism', () => ({
	coy: {},
	dark: {},
}));
// Polyfill TextEncoder/TextDecoder for libraries expecting Web APIs in Node
// react-router (and other libs) may access TextEncoder in test environment
const { TextEncoder, TextDecoder } = require('util');

if (typeof global.TextEncoder === 'undefined') {
	global.TextEncoder = TextEncoder;
}

if (typeof global.TextDecoder === 'undefined') {
	global.TextDecoder = TextDecoder;
}

// (Consolidated above) react-syntax-highlighter mock provides a <pre> element
